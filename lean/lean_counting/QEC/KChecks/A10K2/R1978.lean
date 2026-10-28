import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7912 = true := by
  decide +kernel

theorem tot7912 : totK PA10K2 A10K2.t7912 = [0, 101751147917, 509381178488, 1663267925276, 2103256414358, 765341347135, 57551169768, 0, 0, 0] := by
  decide +kernel

theorem rows7913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7913 = true := by
  decide +kernel

theorem tot7913 : totK PA10K2 A10K2.t7913 = [0, 395640942994, 1732501045401, 1927926285806, 538171142141, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7914 = true := by
  decide +kernel

theorem tot7914 : totK PA10K2 A10K2.t7914 = [0, 283195463782, 1409970571783, 2189462564339, 1119955113506, 116665662649, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7915 = true := by
  decide +kernel

theorem tot7915 : totK PA10K2 A10K2.t7915 = [0, 42391554479, 554961564413, 1795639777007, 1816301265198, 482852233830, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
