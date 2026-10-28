import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7208 = true := by
  decide +kernel

theorem tot7208 : totK PA10K2 A10K2.t7208 = [0, 0, 0, 503825219263, 1911067266417, 1754519931295, 402463673073, 25807237568, 0, 0] := by
  decide +kernel

theorem rows7209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7209 = true := by
  decide +kernel

theorem tot7209 : totK PA10K2 A10K2.t7209 = [0, 0, 0, 670212924710, 2062271187555, 1667306734256, 322811170102, 11740596405, 0, 0] := by
  decide +kernel

theorem rows7210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7210 = true := by
  decide +kernel

theorem tot7210 : totK PA10K2 A10K2.t7210 = [0, 0, 0, 615906445079, 2014191362942, 1700003159977, 317397670818, 14905533017, 0, 0] := by
  decide +kernel

theorem rows7211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7211 = true := by
  decide +kernel

theorem tot7211 : totK PA10K2 A10K2.t7211 = [0, 0, 0, 537440157348, 1916682639389, 1752262882714, 414259603589, 16636608884, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
