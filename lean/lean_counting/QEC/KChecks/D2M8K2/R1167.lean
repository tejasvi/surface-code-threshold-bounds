import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4668 = true := by
  decide +kernel

theorem tot4668 : totK PD2M8K2 D2M8K2.t4668 = [0, 0, 185179805431, 468304997736, 203865317480, 12206147664, 0, 0] := by
  decide +kernel

theorem rows4669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4669 = true := by
  decide +kernel

theorem tot4669 : totK PD2M8K2 D2M8K2.t4669 = [0, 0, 0, 307708670698, 464964019695, 83160639219, 1369150432, 0] := by
  decide +kernel

theorem rows4670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4670 = true := by
  decide +kernel

theorem tot4670 : totK PD2M8K2 D2M8K2.t4670 = [0, 0, 116951795704, 431978911520, 306068321383, 25659940537, 0, 0] := by
  decide +kernel

theorem rows4671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4671 = true := by
  decide +kernel

theorem tot4671 : totK PD2M8K2 D2M8K2.t4671 = [0, 0, 197563487660, 466405750528, 219356956723, 12679943201, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
