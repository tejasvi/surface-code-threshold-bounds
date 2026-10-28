import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4272 = true := by
  decide +kernel

theorem tot4272 : totK PD2M8K2 D2M8K2.t4272 = [0, 0, 93574619190, 383151681548, 395631929977, 45797079592, 0, 0] := by
  decide +kernel

theorem rows4273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4273 = true := by
  decide +kernel

theorem tot4273 : totK PD2M8K2 D2M8K2.t4273 = [0, 0, 162766221026, 444972686267, 283398592031, 29403508898, 0, 0] := by
  decide +kernel

theorem rows4274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4274 = true := by
  decide +kernel

theorem tot4274 : totK PD2M8K2 D2M8K2.t4274 = [0, 0, 174706502236, 479930927363, 236914944882, 11907793430, 0, 0] := by
  decide +kernel

theorem rows4275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4275 = true := by
  decide +kernel

theorem tot4275 : totK PD2M8K2 D2M8K2.t4275 = [0, 0, 0, 203368829527, 461323210912, 225992273066, 21393864572, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
