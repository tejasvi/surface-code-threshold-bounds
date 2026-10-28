import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1180 = true := by
  decide +kernel

theorem tot1180 : totK PD2M8K2 D2M8K2.t1180 = [171339053394, 466746082761, 253606405470, 17567433490, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1181 = true := by
  decide +kernel

theorem tot1181 : totK PD2M8K2 D2M8K2.t1181 = [0, 272450650811, 517945363426, 110237421037, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows1182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1182 = true := by
  decide +kernel

theorem tot1182 : totK PD2M8K2 D2M8K2.t1182 = [136996877329, 423587025232, 317731654275, 32696934811, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1183 = true := by
  decide +kernel

theorem tot1183 : totK PD2M8K2 D2M8K2.t1183 = [176898026587, 440041989652, 252541109810, 26753963771, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
