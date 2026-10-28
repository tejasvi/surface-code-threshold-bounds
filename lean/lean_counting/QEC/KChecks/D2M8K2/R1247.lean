import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4988 = true := by
  decide +kernel

theorem tot4988 : totK PD2M8K2 D2M8K2.t4988 = [0, 0, 80458130419, 403024744328, 385926619733, 40802744086, 0, 0] := by
  decide +kernel

theorem rows4989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4989 = true := by
  decide +kernel

theorem tot4989 : totK PD2M8K2 D2M8K2.t4989 = [0, 0, 0, 217953670138, 503579050436, 159458260193, 5159868635, 0] := by
  decide +kernel

theorem rows4990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4990 = true := by
  decide +kernel

theorem tot4990 : totK PD2M8K2 D2M8K2.t4990 = [0, 0, 171860868172, 436938517332, 270972522444, 30766153524, 0, 0] := by
  decide +kernel

theorem rows4991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4991 = true := by
  decide +kernel

theorem tot4991 : totK PD2M8K2 D2M8K2.t4991 = [0, 0, 192264735692, 477634967045, 224145996492, 12423391470, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
