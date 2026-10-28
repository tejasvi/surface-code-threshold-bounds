import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14704 = true := by
  decide +kernel

theorem tot14704 : totK PD2M8K2 D2M8K2.t14704 = [0, 0, 222671298527, 495494474023, 172302456536, 2992104475, 0, 0] := by
  decide +kernel

theorem rows14705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14705 = true := by
  decide +kernel

theorem tot14705 : totK PD2M8K2 D2M8K2.t14705 = [0, 0, 183243845765, 462044463072, 234230955297, 18184677977, 0, 0] := by
  decide +kernel

theorem rows14706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14706 = true := by
  decide +kernel

theorem tot14706 : totK PD2M8K2 D2M8K2.t14706 = [0, 0, 201544125985, 473772213816, 187430131929, 7668472424, 0, 0] := by
  decide +kernel

theorem rows14707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14707 = true := by
  decide +kernel

theorem tot14707 : totK PD2M8K2 D2M8K2.t14707 = [0, 0, 155489944171, 460447576072, 236780689512, 12866117499, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
