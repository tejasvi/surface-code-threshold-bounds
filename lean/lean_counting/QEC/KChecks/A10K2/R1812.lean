import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7248 = true := by
  decide +kernel

theorem tot7248 : totK PA10K2 A10K2.t7248 = [0, 0, 0, 718386467973, 2217229361329, 1625061695434, 273717982724, 6904928264, 0, 0] := by
  decide +kernel

theorem rows7249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7249 = true := by
  decide +kernel

theorem tot7249 : totK PA10K2 A10K2.t7249 = [0, 0, 378133059829, 1573987487496, 2101487246531, 909810480401, 81102201899, 0, 0, 0] := by
  decide +kernel

theorem rows7250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7250 = true := by
  decide +kernel

theorem tot7250 : totK PA10K2 A10K2.t7250 = [0, 0, 306786434515, 1535603673487, 2248128590113, 954698096297, 69428177062, 0, 0, 0] := by
  decide +kernel

theorem rows7251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7251 = true := by
  decide +kernel

theorem tot7251 : totK PA10K2 A10K2.t7251 = [0, 0, 281984866589, 1262130683328, 1969440554224, 1273844126565, 240156795921, 7047025452, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
