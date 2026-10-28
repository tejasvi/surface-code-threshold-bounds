import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12896 = true := by
  decide +kernel

theorem tot12896 : totK PD2M8K2 D2M8K2.t12896 = [0, 0, 209546919174, 477027199815, 177206938871, 9668735432, 0, 0] := by
  decide +kernel

theorem rows12897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12897 = true := by
  decide +kernel

theorem tot12897 : totK PD2M8K2 D2M8K2.t12897 = [0, 137857439953, 365765571880, 300780655355, 79236280723, 3581949829, 0, 0] := by
  decide +kernel

theorem rows12898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12898 = true := by
  decide +kernel

theorem tot12898 : totK PD2M8K2 D2M8K2.t12898 = [0, 182950191211, 447328388278, 246146164799, 25951503406, 0, 0, 0] := by
  decide +kernel

theorem rows12899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12899 = true := by
  decide +kernel

theorem tot12899 : totK PD2M8K2 D2M8K2.t12899 = [0, 90838862230, 395489178364, 342185409715, 49153160492, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
