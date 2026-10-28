import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3660 = true := by
  decide +kernel

theorem tot3660 : totK PA10K2 A10K2.t3660 = [0, 0, 372612090232, 1206938238020, 1655878843259, 1175391669654, 373594878822, 30176414022, 0, 0] := by
  decide +kernel

theorem rows3661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3661 = true := by
  decide +kernel

theorem tot3661 : totK PA10K2 A10K2.t3661 = [0, 0, 143940004107, 1211687853512, 2199731689745, 944246691235, 79186078253, 0, 0, 0] := by
  decide +kernel

theorem rows3662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3662 = true := by
  decide +kernel

theorem tot3662 : totK PA10K2 A10K2.t3662 = [0, 0, 507669770684, 1622055276736, 1724406664546, 795339434187, 133414678465, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3663 = true := by
  decide +kernel

theorem tot3663 : totK PA10K2 A10K2.t3663 = [0, 0, 282001806592, 1555606190868, 2246029205402, 867145885874, 64215163767, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
