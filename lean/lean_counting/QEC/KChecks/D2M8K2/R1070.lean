import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4280 = true := by
  decide +kernel

theorem tot4280 : totK PD2M8K2 D2M8K2.t4280 = [0, 0, 0, 216896476374, 501528303260, 176173927493, 6864846834, 0] := by
  decide +kernel

theorem rows4281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4281 = true := by
  decide +kernel

theorem tot4281 : totK PD2M8K2 D2M8K2.t4281 = [0, 0, 74723461799, 321118748865, 378420281274, 99965335788, 2333184528, 0] := by
  decide +kernel

theorem rows4282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4282 = true := by
  decide +kernel

theorem tot4282 : totK PD2M8K2 D2M8K2.t4282 = [0, 0, 172864612713, 444724294940, 261972032490, 28734782250, 0, 0] := by
  decide +kernel

theorem rows4283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4283 = true := by
  decide +kernel

theorem tot4283 : totK PD2M8K2 D2M8K2.t4283 = [0, 0, 162473899011, 469802480187, 256890190383, 13839151103, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
