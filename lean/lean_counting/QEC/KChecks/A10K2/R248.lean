import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t992 = true := by
  decide +kernel

theorem tot992 : totK PA10K2 A10K2.t992 = [0, 0, 307513935741, 1173339858217, 1791307515336, 1301059635894, 369877346748, 29010686974, 0, 0] := by
  decide +kernel

theorem rows993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t993 = true := by
  decide +kernel

theorem tot993 : totK PA10K2 A10K2.t993 = [0, 0, 486142690369, 1864564329286, 2028704679138, 544638463799, 24055270135, 0, 0, 0] := by
  decide +kernel

theorem rows994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t994 = true := by
  decide +kernel

theorem tot994 : totK PA10K2 A10K2.t994 = [0, 0, 76784577952, 879183575920, 2207617657785, 1365005125218, 194683471847, 5460492893, 0, 0] := by
  decide +kernel

theorem rows995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t995 = true := by
  decide +kernel

theorem tot995 : totK PA10K2 A10K2.t995 = [0, 0, 473693011392, 1768356709882, 1911231655250, 559884921065, 36596811237, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
