import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2280 = true := by
  decide +kernel

theorem tot2280 : totK PA10K2 A10K2.t2280 = [0, 187384252814, 585918692636, 973600368193, 1641661570929, 1097901344089, 196429719734, 6354482628, 0, 0] := by
  decide +kernel

theorem rows2281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2281 = true := by
  decide +kernel

theorem tot2281 : totK PA10K2 A10K2.t2281 = [0, 289153261105, 1358685191885, 2089672797905, 1160622470913, 192715621067, 7237400819, 0, 0, 0] := by
  decide +kernel

theorem rows2282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2282 = true := by
  decide +kernel

theorem tot2282 : totK PA10K2 A10K2.t2282 = [0, 353634584930, 1450489002351, 2120696436916, 1018450297602, 107381193297, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2283 = true := by
  decide +kernel

theorem tot2283 : totK PA10K2 A10K2.t2283 = [0, 462647355312, 1819057883197, 2020488367674, 631677673600, 31120158474, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
