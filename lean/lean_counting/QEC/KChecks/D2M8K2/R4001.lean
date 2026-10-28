import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16004 = true := by
  decide +kernel

theorem tot16004 : totK PD2M8K2 D2M8K2.t16004 = [0, 0, 197203250466, 467810857477, 230606816173, 16892856297, 0, 0] := by
  decide +kernel

theorem rows16005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16005 = true := by
  decide +kernel

theorem tot16005 : totK PD2M8K2 D2M8K2.t16005 = [0, 0, 71442957365, 341512065341, 401888695145, 85854974987, 1198073392, 0] := by
  decide +kernel

theorem rows16006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16006 = true := by
  decide +kernel

theorem tot16006 : totK PD2M8K2 D2M8K2.t16006 = [0, 0, 0, 225720622193, 482082465230, 168705002333, 9482920370, 0] := by
  decide +kernel

theorem rows16007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16007 = true := by
  decide +kernel

theorem tot16007 : totK PD2M8K2 D2M8K2.t16007 = [0, 0, 158989738083, 406134702413, 261877136056, 57681491579, 2569691499, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
