import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6280 = true := by
  decide +kernel

theorem tot6280 : totK PD2M8K2 D2M8K2.t6280 = [78460481148, 301669468265, 402260544815, 122272648978, 5945454258, 0, 0, 0] := by
  decide +kernel

theorem rows6281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6281 = true := by
  decide +kernel

theorem tot6281 : totK PD2M8K2 D2M8K2.t6281 = [186131925624, 465949887866, 253991010014, 23003581512, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6282 = true := by
  decide +kernel

theorem tot6282 : totK PD2M8K2 D2M8K2.t6282 = [177251648093, 475317728413, 241019211654, 14744288275, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6283 = true := by
  decide +kernel

theorem tot6283 : totK PD2M8K2 D2M8K2.t6283 = [0, 285287040928, 505074760389, 110978798906, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
