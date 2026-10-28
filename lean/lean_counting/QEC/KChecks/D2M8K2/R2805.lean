import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11220 = true := by
  decide +kernel

theorem tot11220 : totK PD2M8K2 D2M8K2.t11220 = [33497804063, 324621474448, 441700916664, 92696531830, 1158555460, 0, 0, 0] := by
  decide +kernel

theorem rows11221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11221 = true := by
  decide +kernel

theorem tot11221 : totK PD2M8K2 D2M8K2.t11221 = [0, 193463248658, 473391339328, 190008289338, 11837410003, 0, 0, 0] := by
  decide +kernel

theorem rows11222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11222 = true := by
  decide +kernel

theorem tot11222 : totK PD2M8K2 D2M8K2.t11222 = [156537680468, 443872289133, 291634856548, 31661436435, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11223 = true := by
  decide +kernel

theorem tot11223 : totK PD2M8K2 D2M8K2.t11223 = [180703873892, 458952987979, 243371296936, 16882193162, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
