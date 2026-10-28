import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t792 = true := by
  decide +kernel

theorem tot792 : totK PA10K2 A10K2.t792 = [0, 335990945730, 1424745908484, 2119871678579, 992436229970, 90992373117, 0, 0, 0, 0] := by
  decide +kernel

theorem rows793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t793 = true := by
  decide +kernel

theorem tot793 : totK PA10K2 A10K2.t793 = [0, 222213893912, 1260893078081, 2109722797705, 1195653690565, 196316171575, 7151180950, 0, 0, 0] := by
  decide +kernel

theorem rows794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t794 = true := by
  decide +kernel

theorem tot794 : totK PA10K2 A10K2.t794 = [0, 341319041492, 1422085949181, 2101144877848, 1059402563164, 133355657770, 0, 0, 0, 0] := by
  decide +kernel

theorem rows795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t795 = true := by
  decide +kernel

theorem tot795 : totK PA10K2 A10K2.t795 = [0, 520886496104, 1917119130999, 1931608841815, 506567678285, 18905173144, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
