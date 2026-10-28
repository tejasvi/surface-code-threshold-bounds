import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4704 = true := by
  decide +kernel

theorem tot4704 : totK PA10K2 A10K2.t4704 = [0, 0, 0, 433370387576, 1707692348476, 1997311414583, 669252246594, 55103251982, 0, 0] := by
  decide +kernel

theorem rows4705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4705 = true := by
  decide +kernel

theorem tot4705 : totK PA10K2 A10K2.t4705 = [0, 0, 0, 538556721908, 1931507613553, 1859160931752, 409220633836, 12917769548, 0, 0] := by
  decide +kernel

theorem rows4706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4706 = true := by
  decide +kernel

theorem tot4706 : totK PA10K2 A10K2.t4706 = [0, 0, 0, 0, 582043988078, 1969235578087, 1644522720113, 390759204182, 25565504801, 0] := by
  decide +kernel

theorem rows4707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4707 = true := by
  decide +kernel

theorem tot4707 : totK PA10K2 A10K2.t4707 = [0, 0, 0, 440341764664, 1537882640294, 1660307598581, 822276544692, 155626451676, 5453062850, 0] := by
  decide +kernel

end QECKChecks.A10K2
