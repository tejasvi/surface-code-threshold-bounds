import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t956 = true := by
  decide +kernel

theorem tot956 : totK PD2M8K2 D2M8K2.t956 = [0, 0, 337046550104, 511344418822, 61675489308, 0, 0, 0] := by
  decide +kernel

theorem rows957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t957 = true := by
  decide +kernel

theorem tot957 : totK PD2M8K2 D2M8K2.t957 = [123289061099, 276817064671, 183838928217, 238218039948, 77815836308, 1415142070, 0, 0] := by
  decide +kernel

theorem rows958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t958 = true := by
  decide +kernel

theorem tot958 : totK PD2M8K2 D2M8K2.t958 = [192623677777, 451598235750, 226237460099, 17111991321, 0, 0, 0, 0] := by
  decide +kernel

theorem rows959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t959 = true := by
  decide +kernel

theorem tot959 : totK PD2M8K2 D2M8K2.t959 = [94063291375, 402946510529, 348379864686, 41917233379, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
