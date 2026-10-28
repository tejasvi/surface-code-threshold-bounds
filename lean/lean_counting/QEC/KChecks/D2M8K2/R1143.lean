import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4572 = true := by
  decide +kernel

theorem tot4572 : totK PD2M8K2 D2M8K2.t4572 = [0, 0, 156228438438, 455919152902, 258905653470, 15484440100, 0, 0] := by
  decide +kernel

theorem rows4573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4573 = true := by
  decide +kernel

theorem tot4573 : totK PD2M8K2 D2M8K2.t4573 = [0, 0, 0, 279342000017, 489532767954, 95462691262, 1334361349, 0] := by
  decide +kernel

theorem rows4574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4574 = true := by
  decide +kernel

theorem tot4574 : totK PD2M8K2 D2M8K2.t4574 = [0, 0, 164429190636, 421678367336, 313248368153, 37080584086, 0, 0] := by
  decide +kernel

theorem rows4575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4575 = true := by
  decide +kernel

theorem tot4575 : totK PD2M8K2 D2M8K2.t4575 = [0, 0, 173992214177, 471665816270, 245502971808, 13912140804, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
