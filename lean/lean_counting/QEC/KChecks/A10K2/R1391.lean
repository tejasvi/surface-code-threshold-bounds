import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5564 = true := by
  decide +kernel

theorem tot5564 : totK PA10K2 A10K2.t5564 = [0, 319364639558, 1059534455684, 1071012764598, 881448949924, 1100244000263, 509383549815, 49180423016, 0, 0] := by
  decide +kernel

theorem rows5565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5565 = true := by
  decide +kernel

theorem tot5565 : totK PA10K2 A10K2.t5565 = [0, 526179114281, 1872929348781, 1888452023937, 482033159219, 18560348465, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5566 = true := by
  decide +kernel

theorem tot5566 : totK PA10K2 A10K2.t5566 = [0, 0, 629498557690, 2035233436996, 1661226848782, 388340422143, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5567 = true := by
  decide +kernel

theorem tot5567 : totK PA10K2 A10K2.t5567 = [0, 292130592925, 1248055075713, 1857624607581, 1137885752372, 190902551853, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
