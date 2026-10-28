import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4536 = true := by
  decide +kernel

theorem tot4536 : totK PD2M8K2 D2M8K2.t4536 = [0, 0, 0, 297340629435, 490179724109, 100973344978, 1242138600, 0] := by
  decide +kernel

theorem rows4537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4537 = true := by
  decide +kernel

theorem tot4537 : totK PD2M8K2 D2M8K2.t4537 = [0, 0, 0, 204253181615, 485846803352, 171019480709, 6138321062, 0] := by
  decide +kernel

theorem rows4538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4538 = true := by
  decide +kernel

theorem tot4538 : totK PD2M8K2 D2M8K2.t4538 = [0, 0, 179245236925, 408330584632, 212337146459, 89124738140, 10633692979, 0] := by
  decide +kernel

theorem rows4539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4539 = true := by
  decide +kernel

theorem tot4539 : totK PD2M8K2 D2M8K2.t4539 = [0, 0, 166012910266, 443140980864, 240568004836, 14644201804, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
