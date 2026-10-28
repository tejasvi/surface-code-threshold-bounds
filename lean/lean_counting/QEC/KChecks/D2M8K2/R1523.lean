import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6092 = true := by
  decide +kernel

theorem tot6092 : totK PD2M8K2 D2M8K2.t6092 = [0, 173274770786, 432864885072, 273026473099, 29963959770, 0, 0, 0] := by
  decide +kernel

theorem rows6093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6093 = true := by
  decide +kernel

theorem tot6093 : totK PD2M8K2 D2M8K2.t6093 = [0, 162480785000, 474025565757, 254914327810, 13912286147, 0, 0, 0] := by
  decide +kernel

theorem rows6094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6094 = true := by
  decide +kernel

theorem tot6094 : totK PD2M8K2 D2M8K2.t6094 = [0, 0, 217607609669, 459894366173, 213861796635, 21391863750, 0, 0] := by
  decide +kernel

theorem rows6095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6095 = true := by
  decide +kernel

theorem tot6095 : totK PD2M8K2 D2M8K2.t6095 = [0, 0, 172344837914, 470374297054, 227314729108, 9283897235, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
