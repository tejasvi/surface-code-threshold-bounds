import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8092 = true := by
  decide +kernel

theorem tot8092 : totK PD2M8K2 D2M8K2.t8092 = [0, 52267668312, 306136032453, 446692003700, 104939782578, 2804045914, 0, 0] := by
  decide +kernel

theorem rows8093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8093 = true := by
  decide +kernel

theorem tot8093 : totK PD2M8K2 D2M8K2.t8093 = [0, 193142683077, 466581738693, 249676375960, 23349548986, 0, 0, 0] := by
  decide +kernel

theorem rows8094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8094 = true := by
  decide +kernel

theorem tot8094 : totK PD2M8K2 D2M8K2.t8094 = [0, 178544988679, 464573787167, 238218255972, 15762929848, 0, 0, 0] := by
  decide +kernel

theorem rows8095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8095 = true := by
  decide +kernel

theorem tot8095 : totK PD2M8K2 D2M8K2.t8095 = [0, 0, 291597225887, 498325716373, 114024439885, 1267860612, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
