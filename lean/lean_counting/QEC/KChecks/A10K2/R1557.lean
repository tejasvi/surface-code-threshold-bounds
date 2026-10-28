import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6228 = true := by
  decide +kernel

theorem tot6228 : totK PA10K2 A10K2.t6228 = [0, 117061640614, 179419417309, 34043221289, 783375085144, 1976363547267, 1193630820382, 193255931756, 5976421810, 0] := by
  decide +kernel

theorem rows6229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6229 = true := by
  decide +kernel

theorem tot6229 : totK PA10K2 A10K2.t6229 = [0, 422960432055, 1770224532232, 1946426293238, 485108072929, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6230 = true := by
  decide +kernel

theorem tot6230 : totK PA10K2 A10K2.t6230 = [0, 295901161011, 1404345967581, 2189848632339, 1075081210550, 89809913823, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6231 = true := by
  decide +kernel

theorem tot6231 : totK PA10K2 A10K2.t6231 = [0, 0, 518459319071, 1824736860791, 1777053690147, 482401725803, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
