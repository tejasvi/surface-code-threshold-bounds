import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14636 = true := by
  decide +kernel

theorem tot14636 : totK PD2M8K2 D2M8K2.t14636 = [0, 186971771778, 473600338841, 251725560937, 23343557212, 0, 0, 0] := by
  decide +kernel

theorem rows14637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14637 = true := by
  decide +kernel

theorem tot14637 : totK PD2M8K2 D2M8K2.t14637 = [0, 171585594055, 461973720978, 240401990228, 13641906834, 0, 0, 0] := by
  decide +kernel

theorem rows14638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14638 = true := by
  decide +kernel

theorem tot14638 : totK PD2M8K2 D2M8K2.t14638 = [0, 0, 294540773501, 495091013122, 111584184483, 1178074134, 0, 0] := by
  decide +kernel

theorem rows14639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14639 = true := by
  decide +kernel

theorem tot14639 : totK PD2M8K2 D2M8K2.t14639 = [0, 0, 189341167168, 473411468051, 190711087220, 12005010568, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
