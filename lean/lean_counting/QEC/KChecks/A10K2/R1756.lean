import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7024 = true := by
  decide +kernel

theorem tot7024 : totK PA10K2 A10K2.t7024 = [0, 0, 632865599096, 1926625404219, 1825841156228, 597191057918, 49164041343, 0, 0, 0] := by
  decide +kernel

theorem rows7025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7025 = true := by
  decide +kernel

theorem tot7025 : totK PA10K2 A10K2.t7025 = [0, 0, 481018340607, 1779481202649, 1895948333488, 530999871247, 32070512872, 0, 0, 0] := by
  decide +kernel

theorem rows7026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7026 = true := by
  decide +kernel

theorem tot7026 : totK PA10K2 A10K2.t7026 = [0, 0, 17059334586, 792110666097, 2120481296773, 1548476013849, 326175134280, 12696458652, 0, 0] := by
  decide +kernel

theorem rows7027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7027 = true := by
  decide +kernel

theorem tot7027 : totK PA10K2 A10K2.t7027 = [0, 0, 272315391523, 1307733081341, 2018980697293, 1067248601489, 123528993283, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
