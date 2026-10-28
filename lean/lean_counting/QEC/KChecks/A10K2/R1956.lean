import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7824 = true := by
  decide +kernel

theorem tot7824 : totK PA10K2 A10K2.t7824 = [0, 0, 59952739641, 701666981189, 2029922840681, 1662066779534, 384986545169, 18457393337, 0, 0] := by
  decide +kernel

theorem rows7825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7825 = true := by
  decide +kernel

theorem tot7825 : totK PA10K2 A10K2.t7825 = [0, 0, 530635337266, 1970883964214, 2000042642462, 553744996440, 24940589961, 0, 0, 0] := by
  decide +kernel

theorem rows7826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7826 = true := by
  decide +kernel

theorem tot7826 : totK PA10K2 A10K2.t7826 = [0, 0, 0, 706262296175, 2285433415251, 1783765905962, 273484307003, 7151180950, 0, 0] := by
  decide +kernel

theorem rows7827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7827 = true := by
  decide +kernel

theorem tot7827 : totK PA10K2 A10K2.t7827 = [0, 0, 540757303387, 1876287828903, 1899464302086, 588350105160, 58379588610, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
