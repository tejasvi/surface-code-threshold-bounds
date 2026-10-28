import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9808 = true := by
  decide +kernel

theorem tot9808 : totK PD2M8K2 D2M8K2.t9808 = [0, 182902957705, 456441954000, 255921471791, 26113002707, 0, 0, 0] := by
  decide +kernel

theorem rows9809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9809 = true := by
  decide +kernel

theorem tot9809 : totK PD2M8K2 D2M8K2.t9809 = [0, 91831780554, 384574494203, 365294112493, 57162121617, 1268739303, 0, 0] := by
  decide +kernel

theorem rows9810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9810 = true := by
  decide +kernel

theorem tot9810 : totK PD2M8K2 D2M8K2.t9810 = [0, 0, 238458223630, 503949486846, 150415391596, 3699256714, 0, 0] := by
  decide +kernel

theorem rows9811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9811 = true := by
  decide +kernel

theorem tot9811 : totK PD2M8K2 D2M8K2.t9811 = [0, 0, 197154483306, 492718744849, 197500377541, 10351277800, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
