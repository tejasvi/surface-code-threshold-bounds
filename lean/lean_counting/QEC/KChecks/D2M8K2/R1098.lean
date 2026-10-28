import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4392 = true := by
  decide +kernel

theorem tot4392 : totK PD2M8K2 D2M8K2.t4392 = [0, 183243395725, 435750783771, 262436416423, 53396918993, 7093008096, 0, 0] := by
  decide +kernel

theorem rows4393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4393 = true := by
  decide +kernel

theorem tot4393 : totK PD2M8K2 D2M8K2.t4393 = [0, 172789162253, 478635082292, 242472764493, 15305734762, 0, 0, 0] := by
  decide +kernel

theorem rows4394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4394 = true := by
  decide +kernel

theorem tot4394 : totK PD2M8K2 D2M8K2.t4394 = [0, 89058976036, 323512630794, 363479022191, 133612180073, 15864095392, 0, 0] := by
  decide +kernel

theorem rows4395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4395 = true := by
  decide +kernel

theorem tot4395 : totK PD2M8K2 D2M8K2.t4395 = [0, 0, 186613946364, 464942743028, 238733269169, 13530797253, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
