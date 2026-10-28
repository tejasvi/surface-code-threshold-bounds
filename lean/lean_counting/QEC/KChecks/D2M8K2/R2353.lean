import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9412 = true := by
  decide +kernel

theorem tot9412 : totK PD2M8K2 D2M8K2.t9412 = [0, 67979873137, 294985636983, 380516263044, 149253262071, 14381175308, 0, 0] := by
  decide +kernel

theorem rows9413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9413 = true := by
  decide +kernel

theorem tot9413 : totK PD2M8K2 D2M8K2.t9413 = [0, 0, 201488598572, 483616626318, 189951844409, 7920387353, 0, 0] := by
  decide +kernel

theorem rows9414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9414 = true := by
  decide +kernel

theorem tot9414 : totK PD2M8K2 D2M8K2.t9414 = [0, 113043372566, 349145067626, 342764771660, 88318611827, 1409560813, 0, 0] := by
  decide +kernel

theorem rows9415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9415 = true := by
  decide +kernel

theorem tot9415 : totK PD2M8K2 D2M8K2.t9415 = [0, 160280352598, 434105539821, 271891360765, 29722551510, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
