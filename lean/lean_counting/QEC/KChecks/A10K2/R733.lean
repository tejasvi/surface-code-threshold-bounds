import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2932 = true := by
  decide +kernel

theorem tot2932 : totK PA10K2 A10K2.t2932 = [0, 417526276724, 1780469735850, 2102065222677, 719763042701, 56230348346, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2933 = true := by
  decide +kernel

theorem tot2933 : totK PA10K2 A10K2.t2933 = [0, 0, 500672986451, 1873795595090, 1821509355829, 480306457099, 30780440178, 0, 0, 0] := by
  decide +kernel

theorem rows2934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2934 = true := by
  decide +kernel

theorem tot2934 : totK PA10K2 A10K2.t2934 = [0, 265289717592, 1387216571363, 2169019533438, 987663556330, 96930777966, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2935 = true := by
  decide +kernel

theorem tot2935 : totK PA10K2 A10K2.t2935 = [0, 505106609141, 1839495065434, 1989976104657, 623120642492, 43616912092, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
