import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4436 = true := by
  decide +kernel

theorem tot4436 : totK PA10K2 A10K2.t4436 = [0, 112276258614, 665959186055, 1843460369396, 1781438269354, 432251438288, 25295400199, 0, 0, 0] := by
  decide +kernel

theorem rows4437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4437 = true := by
  decide +kernel

theorem tot4437 : totK PA10K2 A10K2.t4437 = [0, 482167785330, 1865826917252, 2088199793152, 647074699821, 39617485910, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4438 = true := by
  decide +kernel

theorem tot4438 : totK PA10K2 A10K2.t4438 = [0, 0, 711111533639, 2178763675820, 1766332502952, 365121891548, 12692412833, 0, 0, 0] := by
  decide +kernel

theorem rows4439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4439 = true := by
  decide +kernel

theorem tot4439 : totK PA10K2 A10K2.t4439 = [0, 538423298425, 1833435906361, 1873907377103, 647161095376, 67339588866, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
