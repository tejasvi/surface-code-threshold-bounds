import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3836 = true := by
  decide +kernel

theorem tot3836 : totK PA10K2 A10K2.t3836 = [0, 0, 291829445300, 1220031361361, 1860548528590, 1125141746004, 177038838965, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3837 = true := by
  decide +kernel

theorem tot3837 : totK PA10K2 A10K2.t3837 = [0, 0, 454090662132, 1777011961057, 2002423637100, 575086181394, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows3838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3838 = true := by
  decide +kernel

theorem tot3838 : totK PA10K2 A10K2.t3838 = [0, 0, 0, 662594934524, 2017398589165, 1661995836908, 360037145407, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3839 = true := by
  decide +kernel

theorem tot3839 : totK PA10K2 A10K2.t3839 = [0, 0, 266026540485, 1131374119372, 1866143314297, 1241219531797, 208371181665, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
