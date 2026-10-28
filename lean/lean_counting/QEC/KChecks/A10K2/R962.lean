import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3848 = true := by
  decide +kernel

theorem tot3848 : totK PA10K2 A10K2.t3848 = [0, 0, 0, 454666523320, 1807312179095, 1960693876290, 440862146689, 25686058060, 0, 0] := by
  decide +kernel

theorem rows3849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3849 = true := by
  decide +kernel

theorem tot3849 : totK PA10K2 A10K2.t3849 = [0, 0, 0, 187747219659, 1242401279517, 2288496601836, 1010856773296, 101461880856, 0, 0] := by
  decide +kernel

theorem rows3850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3850 = true := by
  decide +kernel

theorem tot3850 : totK PA10K2 A10K2.t3850 = [0, 0, 0, 478652515807, 1785067989525, 1758658589230, 560887506849, 111845698701, 5447185874, 0] := by
  decide +kernel

theorem rows3851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3851 = true := by
  decide +kernel

theorem tot3851 : totK PA10K2 A10K2.t3851 = [0, 0, 0, 294997606512, 1471673057746, 2122479696628, 776806928190, 50033367339, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
