import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4024 = true := by
  decide +kernel

theorem tot4024 : totK PD2M8K2 D2M8K2.t4024 = [0, 138925489298, 358735788717, 316599098953, 83427647615, 3215984770, 0, 0] := by
  decide +kernel

theorem rows4025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4025 = true := by
  decide +kernel

theorem tot4025 : totK PD2M8K2 D2M8K2.t4025 = [0, 159120742310, 445365109203, 284999549727, 30620959717, 0, 0, 0] := by
  decide +kernel

theorem rows4026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4026 = true := by
  decide +kernel

theorem tot4026 : totK PD2M8K2 D2M8K2.t4026 = [0, 124921220308, 438545795623, 309794495285, 26105447852, 0, 0, 0] := by
  decide +kernel

theorem rows4027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4027 = true := by
  decide +kernel

theorem tot4027 : totK PD2M8K2 D2M8K2.t4027 = [0, 0, 215565078103, 489703852745, 184688737354, 8199159193, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
