import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9912 = true := by
  decide +kernel

theorem tot9912 : totK PD2M8K2 D2M8K2.t9912 = [0, 0, 89419883219, 384236685554, 393333083967, 42332102462, 0, 0] := by
  decide +kernel

theorem rows9913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9913 = true := by
  decide +kernel

theorem tot9913 : totK PD2M8K2 D2M8K2.t9913 = [0, 0, 190505109314, 466718232002, 245333895803, 16613643810, 0, 0] := by
  decide +kernel

theorem rows9914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9914 = true := by
  decide +kernel

theorem tot9914 : totK PD2M8K2 D2M8K2.t9914 = [0, 0, 195623569483, 473588215735, 219141027664, 14815639298, 0, 0] := by
  decide +kernel

theorem rows9915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9915 = true := by
  decide +kernel

theorem tot9915 : totK PD2M8K2 D2M8K2.t9915 = [0, 0, 162208147189, 465890685572, 240596986956, 12393377103, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
