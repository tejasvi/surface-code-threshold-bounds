import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10140 = true := by
  decide +kernel

theorem tot10140 : totK PD2M8K2 D2M8K2.t10140 = [0, 165480432833, 442962122051, 271460821508, 30343566252, 0, 0, 0] := by
  decide +kernel

theorem rows10141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10141 = true := by
  decide +kernel

theorem tot10141 : totK PD2M8K2 D2M8K2.t10141 = [0, 159043362654, 468195623815, 266812447765, 15130787922, 0, 0, 0] := by
  decide +kernel

theorem rows10142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10142 = true := by
  decide +kernel

theorem tot10142 : totK PD2M8K2 D2M8K2.t10142 = [0, 0, 287360501536, 512408217985, 103280865360, 1096505104, 0, 0] := by
  decide +kernel

theorem rows10143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10143 = true := by
  decide +kernel

theorem tot10143 : totK PD2M8K2 D2M8K2.t10143 = [0, 0, 211028952116, 493289805245, 172256565948, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
