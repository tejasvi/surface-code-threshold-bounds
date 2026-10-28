import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4064 = true := by
  decide +kernel

theorem tot4064 : totK PA10K2 A10K2.t4064 = [0, 0, 0, 498888101680, 1917716105421, 2046526663845, 534969042148, 18175333846, 0, 0] := by
  decide +kernel

theorem rows4065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4065 = true := by
  decide +kernel

theorem tot4065 : totK PA10K2 A10K2.t4065 = [0, 0, 417243045409, 1515490283922, 1609205755402, 804686473286, 368293964945, 44456804615, 0, 0] := by
  decide +kernel

theorem rows4066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4066 = true := by
  decide +kernel

theorem tot4066 : totK PA10K2 A10K2.t4066 = [0, 0, 308204874177, 1423960852867, 2167901460719, 1014930237324, 83119020464, 0, 0, 0] := by
  decide +kernel

theorem rows4067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4067 = true := by
  decide +kernel

theorem tot4067 : totK PA10K2 A10K2.t4067 = [0, 0, 188085480274, 921817091523, 1801899889968, 1488347540433, 320001703182, 11991740650, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
