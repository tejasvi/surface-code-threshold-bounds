import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10256 = true := by
  decide +kernel

theorem tot10256 : totK PD2M8K2 D2M8K2.t10256 = [0, 0, 163952137065, 440473555654, 273025212267, 26327014289, 0, 0] := by
  decide +kernel

theorem rows10257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10257 = true := by
  decide +kernel

theorem tot10257 : totK PD2M8K2 D2M8K2.t10257 = [0, 0, 90952881055, 421723792409, 350153670400, 31661266998, 0, 0] := by
  decide +kernel

theorem rows10258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10258 = true := by
  decide +kernel

theorem tot10258 : totK PD2M8K2 D2M8K2.t10258 = [0, 0, 0, 277355421633, 521734018677, 102310198174, 1415142070, 0] := by
  decide +kernel

theorem rows10259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10259 = true := by
  decide +kernel

theorem tot10259 : totK PD2M8K2 D2M8K2.t10259 = [0, 0, 196606120335, 463976242709, 238629288891, 22922743895, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
