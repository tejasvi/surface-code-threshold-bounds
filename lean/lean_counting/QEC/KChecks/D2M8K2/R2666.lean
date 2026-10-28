import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10664 = true := by
  decide +kernel

theorem tot10664 : totK PD2M8K2 D2M8K2.t10664 = [0, 0, 173789758966, 469302529408, 234841338997, 13271230369, 0, 0] := by
  decide +kernel

theorem rows10665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10665 = true := by
  decide +kernel

theorem tot10665 : totK PD2M8K2 D2M8K2.t10665 = [0, 0, 82226460504, 326102440557, 382603580814, 85672030047, 1369150432, 0] := by
  decide +kernel

theorem rows10666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10666 = true := by
  decide +kernel

theorem tot10666 : totK PD2M8K2 D2M8K2.t10666 = [0, 0, 29606877869, 343471910916, 474882803140, 51772928994, 0, 0] := by
  decide +kernel

theorem rows10667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10667 = true := by
  decide +kernel

theorem tot10667 : totK PD2M8K2 D2M8K2.t10667 = [0, 0, 194307220396, 482163169311, 205950468162, 5046664058, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
