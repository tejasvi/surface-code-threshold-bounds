import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5428 = true := by
  decide +kernel

theorem tot5428 : totK PD2M8K2 D2M8K2.t5428 = [0, 0, 164043053881, 467985459071, 260541801655, 15809550548, 0, 0] := by
  decide +kernel

theorem rows5429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5429 = true := by
  decide +kernel

theorem tot5429 : totK PD2M8K2 D2M8K2.t5429 = [0, 0, 0, 275609986757, 493253659597, 118372861751, 1268739303, 0] := by
  decide +kernel

theorem rows5430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5430 = true := by
  decide +kernel

theorem tot5430 : totK PD2M8K2 D2M8K2.t5430 = [0, 0, 0, 181886986165, 491464508673, 202244382383, 6298052033, 0] := by
  decide +kernel

theorem rows5431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5431 = true := by
  decide +kernel

theorem tot5431 : totK PD2M8K2 D2M8K2.t5431 = [0, 0, 0, 172463987439, 472455115861, 211441881433, 13160704066, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
