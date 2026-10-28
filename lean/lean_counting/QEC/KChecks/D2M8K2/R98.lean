import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t392 = true := by
  decide +kernel

theorem tot392 : totK PD2M8K2 D2M8K2.t392 = [68091752397, 233275800288, 390310476967, 195239758216, 10993724876, 0, 0, 0] := by
  decide +kernel

theorem rows393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t393 = true := by
  decide +kernel

theorem tot393 : totK PD2M8K2 D2M8K2.t393 = [177305820618, 460429012865, 247431665781, 22509452149, 0, 0, 0, 0] := by
  decide +kernel

theorem rows394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t394 = true := by
  decide +kernel

theorem tot394 : totK PD2M8K2 D2M8K2.t394 = [178289016479, 474684657630, 232537109453, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t395 = true := by
  decide +kernel

theorem tot395 : totK PD2M8K2 D2M8K2.t395 = [0, 278992148720, 500710052118, 108807974994, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
