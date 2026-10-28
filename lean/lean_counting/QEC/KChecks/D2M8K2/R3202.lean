import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12808 = true := by
  decide +kernel

theorem tot12808 : totK PD2M8K2 D2M8K2.t12808 = [0, 0, 230760103328, 494734373111, 172947675574, 5133256353, 0, 0] := by
  decide +kernel

theorem rows12809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12809 = true := by
  decide +kernel

theorem tot12809 : totK PD2M8K2 D2M8K2.t12809 = [0, 0, 193224851784, 459415269351, 210926869230, 13270058854, 0, 0] := by
  decide +kernel

theorem rows12810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12810 = true := by
  decide +kernel

theorem tot12810 : totK PD2M8K2 D2M8K2.t12810 = [0, 0, 194821546304, 473632761706, 210485703490, 12361325328, 0, 0] := by
  decide +kernel

theorem rows12811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12811 = true := by
  decide +kernel

theorem tot12811 : totK PD2M8K2 D2M8K2.t12811 = [0, 0, 184485388492, 455915725944, 260892973300, 25836559845, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
