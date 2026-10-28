import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t924 = true := by
  decide +kernel

theorem tot924 : totK PA10K2 A10K2.t924 = [0, 437668207111, 1766704176598, 2073183325020, 728900274790, 56072420874, 0, 0, 0, 0] := by
  decide +kernel

theorem rows925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t925 = true := by
  decide +kernel

theorem tot925 : totK PA10K2 A10K2.t925 = [0, 0, 594495347213, 1984342720765, 1766885705612, 370294498182, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t926 = true := by
  decide +kernel

theorem tot926 : totK PA10K2 A10K2.t926 = [0, 560104966586, 1891167655082, 1885331104647, 615794173744, 55733977678, 0, 0, 0, 0] := by
  decide +kernel

theorem rows927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t927 = true := by
  decide +kernel

theorem tot927 : totK PA10K2 A10K2.t927 = [0, 331206821931, 1535358312045, 2178885139057, 875513065661, 68436273338, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
