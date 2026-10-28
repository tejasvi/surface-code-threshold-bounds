import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3684 = true := by
  decide +kernel

theorem tot3684 : totK PA10K2 A10K2.t3684 = [0, 266424507814, 1191913330826, 1930824984825, 1163975078491, 220566368028, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3685 = true := by
  decide +kernel

theorem tot3685 : totK PA10K2 A10K2.t3685 = [0, 0, 456595089064, 1780461345910, 1944911869404, 532796141402, 32520423844, 0, 0, 0] := by
  decide +kernel

theorem rows3686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3686 = true := by
  decide +kernel

theorem tot3686 : totK PA10K2 A10K2.t3686 = [0, 0, 456732611805, 1811946231203, 2015435335177, 580773551410, 32885668568, 0, 0, 0] := by
  decide +kernel

theorem rows3687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3687 = true := by
  decide +kernel

theorem tot3687 : totK PA10K2 A10K2.t3687 = [0, 0, 0, 537900582122, 1893546985656, 1642600830251, 410925372136, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
