<?xml version="1.0" encoding="US-ASCII" ?>
<%@ page language="java" contentType="text/html; charset=US-ASCII" pageEncoding="US-ASCII" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=US-ASCII"/>
<meta name="google-site-verification" content="LOqHmNdKeDwTTSz30qyW1RNLskaB1UonksxJUmnMlSc"/>
<title>Joogie - Infeasible Code Detection for Java</title>
<link rel="stylesheet" href="css/joogie-ws.css"/>
<link rel="stylesheet" href="lib/codemirror/codemirror.css"/>
<script src="lib/codemirror/codemirror.js"></script>
<script src="lib/codemirror/clike.js"></script>
<style>
.CodeMirror {
	border: 2px inset #dee;
}
</style>
</head>
<body>

	<div id="site">
		<div id="logo">
			<a href="./"><img alt="logo" border="0" src="img/logo.png"
				width="50px"/></a>
		</div>
		<div id="title">
			<h1 class="title">Joogie</h1>
			<h2 class="title">Infeasible Code Detection for Java</h2>
		</div>
		<div id="prompt">
			<img alt="Write some Java code here!" src="img/prompt.png"/>
		</div>
		<div id="content">
			<form id="form" action="./index" method="post">
				<c:choose>
					<c:when test="${'POST' == pageContext.request.method}">
						<c:set var="code" value="${param.code}"/>
					</c:when>
					<c:otherwise>
						<c:set var="code" value="${requestScope.example}"/>
					</c:otherwise>
				</c:choose>
				<textarea id="code" name="code"><c:out value="${code}"/></textarea>
				<c:if test="${'POST' == pageContext.request.method}">
					<c:if test="${null != requestScope.error}">
						<table border="0" width="100%" style="background-color: #FFFF80; font-family: Courier;">
							<tr>
								<td width="100%"><c:out value="${requestScope.error}"/></td>
							</tr>
						</table>					
					</c:if>
					<c:if test="${null != requestScope.report}">
						<p><b>Results</b></p>
						<c:choose>
							<c:when test="${0 == requestScope.report.getInfeasibleMethodCount()}">
								<table border="0" width="100%" style="background-color: #D6FFD6; font-family: Courier;">
									<tr>
										<td width="100%">Joogie did not find infeasible code in this program.</td>
									</tr>
								</table>
							</c:when>
							<c:otherwise>
								<table border="0" width="100%" style="background-color: #FFB2B2; font-family: Courier;">
								<c:forEach var="method" items="${requestScope.report.getInfeasibleMethods()}">
									<c:forEach var="block" items="${method.getInfeasibleBlocks()}">
										<c:set var="line" value="unknown"/>
										<c:if test="${null != block.getLocationTag()}">
											<c:set var="line" value="${block.getLocationTag().getLineNumber()}"/>
										</c:if>
										<tr>
											<td>infeasible code in method <b><c:out value="${method.getFriendlyName()}"/></b> near line <c:out value="${line}"/></td>
										</tr>
									</c:forEach>
								</c:forEach>
								</table>
							</c:otherwise>
						</c:choose>
						<p><b>Statistics</b></p>
						<table border="0" width="100%" style="background-color: #CCE6FF; font-family: Courier;">
							<tr>
								<td width="30%">Methods (incl. constructor)</td>
								<td><c:out value="${report.getMethodCount() - 1}"/></td>
							</tr>
							<tr>
								<td width="25%">Infeasible Methods</td>
								<td><c:out value="${report.getInfeasibleMethodCount()}"/></td>
							</tr>
							<tr>
								<td width="25%">Queries</td>
								<td><c:out value="${report.getQueryCount()}"/></td>
							</tr>
							<tr>
								<td width="25%">Avg. Queries per Method</td>
								<td><c:out value="${report.getAvgQueryCount()}"/></td>
							</tr>
							<tr>
								<td width="25%">Avg. Time per Method</td>
								<td><c:out value="${report.getAvgTimePerMethod()} ms"/></td>
							</tr>
							<tr>
								<td width="25%">Avg. Time per Query</td>
								<td><c:out value="${report.getAvgTimePerQuery()} ms"/></td>
							</tr>
							<tr>
								<td width="25%">TOTAL TIME</td>
								<td><c:out value="${report.getTime()} ms"/></td>
							</tr>
						</table>
					</c:if>
				</c:if>
					
				<p>Does this program contain <b>Infeasible Code?</b></p>
				<p>
					<a href="#" class="button"
						onclick="document.getElementById('form').submit()">Ask <b>Joogie</b>!</a>
					&nbsp; or <a href="./">Load New Example</a> |
						      <a href="http://code.google.com/p/joogie/">Get More Information</a>
				</p>
			</form>
		</div>
		<div id="footer">
			<div style="float: left">
			<iframe
				src="http://www.facebook.com/plugins/like.php?href=http%3A%2F%2Fwww.joogie.org&amp;layout=button_count&amp;show_faces=true&amp;action=like&amp;colorscheme=light&amp;height=20&amp;width=100"
				scrolling="no" frameborder="0"
				style="border: none; overflow: hidden; height: 20px; width: 100px;"
				allowTransparency="true"></iframe>
			</div>

			<div style="float: left">
			<a href="https://twitter.com/share" class="twitter-share-button"
				data-url="http://www.joogie.org/">Tweet</a>
			<script>
				!function(d, s, id) {
					var js, fjs = d.getElementsByTagName(s)[0], p = /^http:/
							.test(d.location) ? 'http' : 'https';
					if (!d.getElementById(id)) {
						js = d.createElement(s);
						js.id = id;
						js.src = p + '://platform.twitter.com/widgets.js';
						fjs.parentNode.insertBefore(js, fjs);
					}
				}(document, 'script', 'twitter-wjs');
			</script>
			</div>
			
			<div style="float: left; display: block;">
			<script type="text/javascript"
				src="https://apis.google.com/js/plusone.js"></script>
			<g:plusone size="medium" annotation="bubble" width="300"
				href="http://www.joogie.org/"></g:plusone>
			</div>
		</div>
	</div>

	<script>
		var editor = CodeMirror.fromTextArea(document.getElementById("code"), {
			lineNumbers : true,
			matchBrackets : true,
			mode : "text/x-java"
		});
	</script>

</body>
</html>
