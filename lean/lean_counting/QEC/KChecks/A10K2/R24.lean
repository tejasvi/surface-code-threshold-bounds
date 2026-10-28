import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows96 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t96 = true := by
  decide +kernel

theorem tot96 : totK PA10K2 A10K2.t96 = [431051959020, 1693457852746, 1922547159384, 643746465714, 52230029129, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows97 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t97 = true := by
  decide +kernel

theorem tot97 : totK PA10K2 A10K2.t97 = [206359410798, 1364287420176, 2215368638159, 923759655428, 67340780067, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows98 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t98 = true := by
  decide +kernel

theorem tot98 : totK PA10K2 A10K2.t98 = [0, 497063160316, 1859722016156, 1838169012004, 477485673245, 26944025047, 0, 0, 0, 0] := by
  decide +kernel

theorem rows99 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t99 = true := by
  decide +kernel

theorem tot99 : totK PA10K2 A10K2.t99 = [0, 267465855910, 1337928725247, 1978684858619, 995953889951, 175493718413, 15171143123, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
