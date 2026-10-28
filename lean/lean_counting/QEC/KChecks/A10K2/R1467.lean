import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5868 = true := by
  decide +kernel

theorem tot5868 : totK PA10K2 A10K2.t5868 = [0, 0, 311053418201, 1530755542201, 2123818002420, 760448147641, 45913727628, 0, 0, 0] := by
  decide +kernel

theorem rows5869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5869 = true := by
  decide +kernel

theorem tot5869 : totK PA10K2 A10K2.t5869 = [0, 0, 0, 701887470531, 2158002922293, 1559700293544, 262931578621, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5870 = true := by
  decide +kernel

theorem tot5870 : totK PA10K2 A10K2.t5870 = [0, 0, 0, 457009002235, 1744258600796, 1915692859956, 511169349156, 31987876949, 0, 0] := by
  decide +kernel

theorem rows5871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5871 = true := by
  decide +kernel

theorem tot5871 : totK PA10K2 A10K2.t5871 = [0, 0, 0, 521272947981, 1793078370937, 1827991230709, 477644083395, 32480588830, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
