import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7204 = true := by
  decide +kernel

theorem tot7204 : totK PD2M8K2 D2M8K2.t7204 = [0, 0, 84003304347, 316962222359, 368934745172, 94505230171, 3804183361, 0] := by
  decide +kernel

theorem rows7205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7205 = true := by
  decide +kernel

theorem tot7205 : totK PD2M8K2 D2M8K2.t7205 = [0, 0, 170002012720, 476781612703, 244872173396, 11438047831, 0, 0] := by
  decide +kernel

theorem rows7206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7206 = true := by
  decide +kernel

theorem tot7206 : totK PD2M8K2 D2M8K2.t7206 = [0, 0, 210706916207, 486785197169, 189036399927, 10219142908, 0, 0] := by
  decide +kernel

theorem rows7207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7207 = true := by
  decide +kernel

theorem tot7207 : totK PD2M8K2 D2M8K2.t7207 = [0, 0, 172057267468, 463503744117, 258389209716, 16858032229, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
