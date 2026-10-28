import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6852 = true := by
  decide +kernel

theorem tot6852 : totK PA10K2 A10K2.t6852 = [0, 0, 225546360787, 1244770913405, 2129460835080, 1177696935529, 191175309826, 7151180950, 0, 0] := by
  decide +kernel

theorem rows6853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6853 = true := by
  decide +kernel

theorem tot6853 : totK PA10K2 A10K2.t6853 = [0, 0, 370163216264, 1444691208957, 1906560661762, 915526170066, 112752229140, 0, 0, 0] := by
  decide +kernel

theorem rows6854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6854 = true := by
  decide +kernel

theorem tot6854 : totK PA10K2 A10K2.t6854 = [0, 0, 582063553146, 2072214962661, 1941785455365, 413125702490, 12557093595, 0, 0, 0] := by
  decide +kernel

theorem rows6855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6855 = true := by
  decide +kernel

theorem tot6855 : totK PA10K2 A10K2.t6855 = [0, 128889292512, 621747612361, 1535922900508, 1885518138005, 788623330742, 62632138461, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
