import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4276 = true := by
  decide +kernel

theorem tot4276 : totK PD2M8K2 D2M8K2.t4276 = [0, 0, 0, 185637529843, 477777822370, 217484961727, 9335631830, 0] := by
  decide +kernel

theorem rows4277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4277 = true := by
  decide +kernel

theorem tot4277 : totK PD2M8K2 D2M8K2.t4277 = [0, 0, 134860001436, 350158705058, 298705819957, 113467016161, 6756203132, 0] := by
  decide +kernel

theorem rows4278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4278 = true := by
  decide +kernel

theorem tot4278 : totK PD2M8K2 D2M8K2.t4278 = [0, 0, 165441188316, 449863224575, 283625124822, 30437197709, 0, 0] := by
  decide +kernel

theorem rows4279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4279 = true := by
  decide +kernel

theorem tot4279 : totK PD2M8K2 D2M8K2.t4279 = [0, 0, 139706554438, 447995361218, 289122984801, 23069397041, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
