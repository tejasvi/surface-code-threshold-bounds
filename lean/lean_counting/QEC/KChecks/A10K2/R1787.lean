import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7148 = true := by
  decide +kernel

theorem tot7148 : totK PA10K2 A10K2.t7148 = [0, 0, 324860638317, 1582650936512, 2174588419301, 779821274894, 56233027364, 0, 0, 0] := by
  decide +kernel

theorem rows7149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7149 = true := by
  decide +kernel

theorem tot7149 : totK PA10K2 A10K2.t7149 = [0, 0, 0, 470867690646, 1810585016297, 1844411234032, 490569812247, 30831673886, 0, 0] := by
  decide +kernel

theorem rows7150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7150 = true := by
  decide +kernel

theorem tot7150 : totK PA10K2 A10K2.t7150 = [0, 0, 251705348851, 1268162541145, 2056978396525, 1018554612757, 77294390093, 0, 0, 0] := by
  decide +kernel

theorem rows7151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7151 = true := by
  decide +kernel

theorem tot7151 : totK PA10K2 A10K2.t7151 = [0, 0, 527268749223, 1716672431101, 1790069596279, 654408395656, 100089069692, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
