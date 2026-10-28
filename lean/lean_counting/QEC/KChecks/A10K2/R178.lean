import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t712 = true := by
  decide +kernel

theorem tot712 : totK PA10K2 A10K2.t712 = [0, 0, 275317523177, 1431535652288, 2110526080137, 810926431377, 65988555795, 0, 0, 0] := by
  decide +kernel

theorem rows713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t713 = true := by
  decide +kernel

theorem tot713 : totK PA10K2 A10K2.t713 = [0, 0, 175071977364, 828150310967, 1749857958425, 1410841485328, 383057631108, 30074883546, 0, 0] := by
  decide +kernel

theorem rows714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t714 = true := by
  decide +kernel

theorem tot714 : totK PA10K2 A10K2.t714 = [0, 0, 431965250773, 1721593615677, 1921977419329, 546048616292, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t715 = true := by
  decide +kernel

theorem tot715 : totK PA10K2 A10K2.t715 = [0, 0, 90301531036, 872707931189, 1914128540789, 1292975811723, 308234442938, 24969229125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
