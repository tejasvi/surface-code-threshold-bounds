import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5468 = true := by
  decide +kernel

theorem tot5468 : totK PD2M8K2 D2M8K2.t5468 = [0, 0, 0, 203000045269, 476864885348, 202972074210, 11428133182, 0] := by
  decide +kernel

theorem rows5469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5469 = true := by
  decide +kernel

theorem tot5469 : totK PD2M8K2 D2M8K2.t5469 = [0, 0, 0, 180336160463, 481860434296, 228095269336, 8038967699, 0] := by
  decide +kernel

theorem rows5470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5470 = true := by
  decide +kernel

theorem tot5470 : totK PD2M8K2 D2M8K2.t5470 = [0, 0, 172024371571, 424284138835, 203696362735, 76128663843, 10848362472, 0] := by
  decide +kernel

theorem rows5471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5471 = true := by
  decide +kernel

theorem tot5471 : totK PD2M8K2 D2M8K2.t5471 = [0, 0, 222292746603, 473115235951, 206806168115, 8200314326, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
