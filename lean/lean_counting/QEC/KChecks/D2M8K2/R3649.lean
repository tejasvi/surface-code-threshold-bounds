import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14596 = true := by
  decide +kernel

theorem tot14596 : totK PD2M8K2 D2M8K2.t14596 = [0, 0, 298616258027, 487859444422, 101819018646, 1242138600, 0, 0] := by
  decide +kernel

theorem rows14597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14597 = true := by
  decide +kernel

theorem tot14597 : totK PD2M8K2 D2M8K2.t14597 = [0, 0, 217182288756, 470572534992, 167842274921, 7182288656, 0, 0] := by
  decide +kernel

theorem rows14598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14598 = true := by
  decide +kernel

theorem tot14598 : totK PD2M8K2 D2M8K2.t14598 = [0, 173658224399, 375229005217, 218915565551, 114020532730, 13326740810, 0, 0] := by
  decide +kernel

theorem rows14599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14599 = true := by
  decide +kernel

theorem tot14599 : totK PD2M8K2 D2M8K2.t14599 = [0, 171685786173, 446841297316, 242361651596, 18076889422, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
