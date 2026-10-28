import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9212 = true := by
  decide +kernel

theorem tot9212 : totK PD2M8K2 D2M8K2.t9212 = [0, 157251633541, 430794286320, 275437013819, 55697013673, 1149959346, 0, 0] := by
  decide +kernel

theorem rows9213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9213 = true := by
  decide +kernel

theorem tot9213 : totK PD2M8K2 D2M8K2.t9213 = [0, 177487975125, 451992255299, 253659381888, 18291457038, 0, 0, 0] := by
  decide +kernel

theorem rows9214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9214 = true := by
  decide +kernel

theorem tot9214 : totK PD2M8K2 D2M8K2.t9214 = [0, 80679071701, 413950301124, 375868383622, 42092540810, 0, 0, 0] := by
  decide +kernel

theorem rows9215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9215 = true := by
  decide +kernel

theorem tot9215 : totK PD2M8K2 D2M8K2.t9215 = [0, 0, 214469445431, 496705605725, 164439521090, 5218872685, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
