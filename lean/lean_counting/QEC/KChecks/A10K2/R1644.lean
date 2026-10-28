import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6576 = true := by
  decide +kernel

theorem tot6576 : totK PA10K2 A10K2.t6576 = [0, 0, 580651332193, 1966511704941, 1828967095669, 391354286750, 11740596405, 0, 0, 0] := by
  decide +kernel

theorem rows6577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6577 = true := by
  decide +kernel

theorem tot6577 : totK PA10K2 A10K2.t6577 = [0, 0, 466542609556, 1780353224348, 1977436624816, 554640124230, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows6578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6578 = true := by
  decide +kernel

theorem tot6578 : totK PA10K2 A10K2.t6578 = [0, 0, 512181592957, 1812488663038, 1845644091627, 512358652813, 31607162994, 0, 0, 0] := by
  decide +kernel

theorem rows6579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6579 = true := by
  decide +kernel

theorem tot6579 : totK PA10K2 A10K2.t6579 = [0, 0, 304499308337, 1529850279635, 2079869660766, 666253915368, 51402059204, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
