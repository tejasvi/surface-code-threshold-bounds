import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5316 = true := by
  decide +kernel

theorem tot5316 : totK PD2M8K2 D2M8K2.t5316 = [0, 26952905136, 198833662555, 447704808166, 220603213031, 9353868799, 0, 0] := by
  decide +kernel

theorem rows5317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5317 = true := by
  decide +kernel

theorem tot5317 : totK PD2M8K2 D2M8K2.t5317 = [0, 183499666699, 459388682378, 250257629921, 23042648846, 0, 0, 0] := by
  decide +kernel

theorem rows5318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5318 = true := by
  decide +kernel

theorem tot5318 : totK PD2M8K2 D2M8K2.t5318 = [0, 189716994082, 474387798785, 226234922760, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows5319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5319 = true := by
  decide +kernel

theorem tot5319 : totK PD2M8K2 D2M8K2.t5319 = [0, 38150555787, 313272049649, 448411552899, 95479123081, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
