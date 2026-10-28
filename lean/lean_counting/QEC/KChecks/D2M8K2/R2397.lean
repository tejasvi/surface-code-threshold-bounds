import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9588 = true := by
  decide +kernel

theorem tot9588 : totK PD2M8K2 D2M8K2.t9588 = [169772273150, 441870805477, 274417362848, 30271926621, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9589 = true := by
  decide +kernel

theorem tot9589 : totK PD2M8K2 D2M8K2.t9589 = [123351558152, 436814793497, 319487404048, 27741077662, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9590 = true := by
  decide +kernel

theorem tot9590 : totK PD2M8K2 D2M8K2.t9590 = [0, 203899453666, 483774121893, 189407522627, 9652233629, 0, 0, 0] := by
  decide +kernel

theorem rows9591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9591 = true := by
  decide +kernel

theorem tot9591 : totK PD2M8K2 D2M8K2.t9591 = [87123270202, 342888924397, 372808387164, 93870879020, 3564119920, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
