import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1776 = true := by
  decide +kernel

theorem tot1776 : totK PD2M8K2 D2M8K2.t1776 = [0, 92081819623, 156813554636, 119667328463, 315324254326, 183073852309, 17014456371, 0] := by
  decide +kernel

theorem rows1777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1777 = true := by
  decide +kernel

theorem tot1777 : totK PD2M8K2 D2M8K2.t1777 = [0, 171250058782, 477954235702, 241294000661, 12240561251, 0, 0, 0] := by
  decide +kernel

theorem rows1778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1778 = true := by
  decide +kernel

theorem tot1778 : totK PD2M8K2 D2M8K2.t1778 = [0, 174002787257, 460748970366, 243430762020, 16715323372, 0, 0, 0] := by
  decide +kernel

theorem rows1779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1779 = true := by
  decide +kernel

theorem tot1779 : totK PD2M8K2 D2M8K2.t1779 = [0, 0, 278877782403, 512315820875, 112215006405, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
