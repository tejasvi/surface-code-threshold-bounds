import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5968 = true := by
  decide +kernel

theorem tot5968 : totK PA10K2 A10K2.t5968 = [0, 0, 75421789856, 1279366649211, 2282980767339, 854117288721, 63645606988, 0, 0, 0] := by
  decide +kernel

theorem rows5969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5969 = true := by
  decide +kernel

theorem tot5969 : totK PA10K2 A10K2.t5969 = [0, 455829770507, 1468289410402, 1410736704605, 759059034499, 553672718036, 128644302662, 5676195732, 0, 0] := by
  decide +kernel

theorem rows5970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5970 = true := by
  decide +kernel

theorem tot5970 : totK PA10K2 A10K2.t5970 = [0, 351481254165, 1593288085696, 2095385223493, 811679586724, 71361928948, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5971 = true := by
  decide +kernel

theorem tot5971 : totK PA10K2 A10K2.t5971 = [0, 0, 690082426362, 2121972218805, 1644335137908, 364979344204, 25313348169, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
